include_recipe 'infrastructure::vagrant'
include_recipe 'metatheory::common'

package 'apache2'

# Expose the coq docs in the default virtual host
link 'soft-link-coq-docs-to-apache' do
  target_file '/var/www/html/coq'
  to '/usr/share/doc/coq-theories/html'
end
