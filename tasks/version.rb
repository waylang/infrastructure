require 'colorize'
require 'English'
require 'pathname'

namespace :version do
  def ensure_clean_workspace
    `git diff --quiet`
    unless $CHILD_STATUS.exitstatus == 0
      raise 'There are unstaged changes!'.colorize(color: :red, mode: :bold)
    end

    `git diff --staged --quiet`
    unless $CHILD_STATUS.exitstatus == 0
      raise 'There are uncommitted changes!'.colorize(color: :red, mode: :bold)
    end
  end

  def calculate_new_version(old_version, component_to_bump)
    index_to_bump = %i(major minor patch).index(component_to_bump)
    components = old_version.split('.').map(&:to_i)
    components[index_to_bump] += 1
    ((index_to_bump + 1)...(components.length)).each { |i| components[i] = 0 }
    components.join('.')
  end

  def write_new_version(component_to_bump)
    version_file = Pathname.new(__FILE__).parent.parent + 'version'
    old_version = File.read(version_file).strip
    new_version = calculate_new_version old_version, component_to_bump
    File.open(version_file, 'w') { |f| f.write("#{new_version}\n") }
    new_version
  end

  def commit_and_tag(new_version)
    # Use sh so that failures raise
    sh "git commit -am 'Committing version #{new_version}'"
    sh "git tag -a -m 'Tagging #{new_version}' 'v#{new_version}'"
  end

  def bump_and_tag(component_to_bump)
    ensure_clean_workspace
    new_version = write_new_version(component_to_bump)
    commit_and_tag(new_version)
    puts "Tagged version #{new_version}".colorize(color: :green, mode: :bold)
  end

  desc 'Tag a new major version release'
  task :major do
    bump_and_tag :major
  end

  desc 'Tag a new minor version release'
  task :minor do
    bump_and_tag :minor
  end

  desc 'Tag a new patch version release'
  task :patch do
    bump_and_tag :patch
  end
end
