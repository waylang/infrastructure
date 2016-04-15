require 'spec_helper'

describe 'metatheory::vagrant' do
  let(:hostname) { 'the-hostname' }

  let(:chef_run) do
    ChefSpec::SoloRunner.new do |node|
      node.automatic['hostname'] = hostname
    end.converge(described_recipe)
  end

  it 'includes infrastructure::vagrant' do
    expect(chef_run).to include_recipe('infrastructure::vagrant')
  end

  it 'includes common' do
    expect(chef_run).to include_recipe('metatheory::common')
  end

  it 'installs apache2' do
    expect(chef_run).to install_package('apache2')
  end

  it 'softlinks the coq docs to the apache default virtual host' do
    expect(chef_run).to create_link('soft-link-coq-docs-to-apache').with(
      target_file: '/var/www/html/coq',
      to: '/usr/share/doc/coq-theories/html')
  end
end
